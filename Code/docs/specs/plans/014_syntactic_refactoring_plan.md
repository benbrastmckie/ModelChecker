# Syntactic.py Refactoring Implementation Plan

**Plan ID**: 014  
**Created**: 2025-08-07  
**Status**: Draft  
**Author**: AI Assistant  
**Related**: [008_v1_release_preparation.md](008_v1_release_preparation.md)

## Executive Summary

This plan details the refactoring of `syntactic.py` (895 lines) into a well-organized `syntactic/` subpackage. Following the successful model.py and utils.py refactoring patterns, this plan emphasizes incremental migration with comprehensive dual testing methodology to prevent regressions while handling the complex operator system and parser functionality.

## Current State Analysis

### File Overview
- **Location**: `/src/model_checker/syntactic.py`
- **Size**: 895 lines
- **Dependencies**: Used by all theories for operator registration and formula parsing
- **Critical Functions**: Sentence class, Operator hierarchy, OperatorCollection, Syntax orchestration

### Component Categories

1. **Core Sentence Class** (lines 61-265)
   - `Sentence` class - Core formula representation
   - Infix/prefix notation handling
   - Metadata and semantic binding management

2. **Operator Base Classes** (lines 266-501)
   - `Operator` abstract base class
   - Core operator interface and behavior
   - Instantiation and equality testing

3. **Advanced Operator Support** (lines 502-586)
   - `DefinedOperator` class for complex operators
   - Validation and arity matching
   - Primitive operator definitions

4. **Operator Management** (lines 587-697)
   - `OperatorCollection` registry system
   - Operator registration and lookup
   - Type checking and uniqueness enforcement

5. **Syntax Orchestration** (lines 698-895)
   - `Syntax` class for argument processing
   - Premise and conclusion handling
   - Sentence hierarchy building and validation

6. **Supporting Functions** (lines 46-60)
   - `AtomVal()` and `AtomSort` Z3 integration
   - Core syntactic utilities

### Dependency Analysis

#### Most Critical Dependencies
1. **parse_expression** - Used by Sentence and Syntax for formula parsing
2. **Operator classes** - Used by all theories for operator registration
3. **OperatorCollection** - Core registry used throughout theory system
4. **Syntax** - Main orchestration class used by all examples

#### Import Patterns
```python
# Common imports found in theories:
from model_checker.syntactic import Operator, DefinedOperator
from model_checker.syntactic import OperatorCollection, Syntax
from model_checker import Syntax  # Main import path
from model_checker.theory_lib.logos.operators import LogosOperators
```

## Design Decisions

### Subpackage Structure

```
src/model_checker/syntactic/
├── __init__.py          # Re-export all public classes
├── README.md           # Comprehensive documentation
├── sentence.py         # Sentence class and core formula handling
├── operators.py        # Operator and DefinedOperator base classes  
├── collection.py       # OperatorCollection registry system
├── syntax.py           # Syntax orchestration class
├── atoms.py            # AtomSort and AtomVal utilities
└── tests/
    ├── __init__.py
    ├── test_sentence.py    # Sentence class tests
    ├── test_operators.py   # Operator hierarchy tests
    ├── test_collection.py  # OperatorCollection tests
    ├── test_syntax.py      # Syntax orchestration tests
    └── test_imports.py     # Import validation tests
```

### Migration Strategy

1. **Conservative Splitting**: Keep related functionality together to minimize cross-module dependencies
2. **Backward Compatibility**: Maintain all existing import paths through __init__.py
3. **Incremental Validation**: Test each component move with both test runner and CLI validation
4. **Theory Integration**: Special attention to theory-specific operator integration

### Risk Assessment

#### High Risk Components
1. **Operator hierarchy** - Core to all theory operator definitions
2. **OperatorCollection** - Registry system used throughout theories
3. **Syntax class** - Main orchestration used by all examples
4. **parse_expression integration** - Parser functionality dependencies

#### Medium Risk Components
1. **Sentence class** - Complex formula representation
2. **DefinedOperator** - Advanced operator composition
3. **Z3 integration** - AtomSort and AtomVal usage

#### Low Risk Components
1. **Documentation and comments** - Safe to move
2. **Helper utilities** - Minimal cross-dependencies
3. **Constants and type definitions** - Static definitions

## Implementation Phases

### Phase 3.1: Setup and Baseline (Day 1)

**Tasks**:
1. Create comprehensive baseline
2. Map all syntactic dependencies across theories
3. Create syntactic/ directory structure
4. Write initial test infrastructure

**Testing Protocol**:
```bash
# Baseline capture
mkdir -p docs/specs/baselines/phase3
./run_tests.py --unit --package > docs/specs/baselines/phase3/all_tests.txt 2>&1

# Test operator parsing specifically for each theory
for theory in logos exclusion imposition bimodal; do
  ./dev_cli.py src/model_checker/theory_lib/$theory/examples.py > \
    docs/specs/baselines/phase3/${theory}_operators.txt 2>&1
done

# Test complex formula parsing
for subtheory in counterfactual constitutive extensional modal relevance; do
  ./dev_cli.py src/model_checker/theory_lib/logos/subtheories/$subtheory/examples.py > \
    docs/specs/baselines/phase3/${subtheory}_parsing.txt 2>&1
done

# Map dependencies
grep -r "from.*syntactic import" src/ > docs/specs/baselines/phase3/syntactic_imports.txt
grep -r "import.*syntactic" src/ >> docs/specs/baselines/phase3/syntactic_imports.txt
```

### Phase 3.2: Move Core Atoms and Utilities (Day 2)

**Component**: AtomSort, AtomVal functions
**Target**: syntactic/atoms.py

**Tasks**:
1. Write comprehensive tests for Z3 atom integration
2. Move AtomSort and AtomVal to atoms.py
3. Update imports in syntactic.py
4. Test with theory examples

**Critical Testing**:
```bash
# Test Z3 atom creation
pytest src/model_checker/syntactic/tests/test_atoms.py -v

# Test theory integration
for theory in logos exclusion imposition bimodal; do
  ./dev_cli.py src/model_checker/theory_lib/$theory/examples.py > ${theory}_atoms.txt 2>&1
  grep -E "WARNING|Error|AttributeError" ${theory}_atoms.txt
done
```

### Phase 3.3: Move Sentence Class (Day 3)

**Component**: Sentence class
**Target**: syntactic/sentence.py

**Tasks**:
1. Write tests covering infix/prefix notation handling
2. Move Sentence class with all methods
3. Update imports and validate metadata handling
4. Test formula representation across theories

**Testing Focus**:
- Formula parsing and representation
- Infix/prefix conversion accuracy
- Metadata preservation during processing
- Semantic binding functionality

### Phase 3.4: Move Operator Classes (Day 4)

**Components**: Operator, DefinedOperator classes
**Target**: syntactic/operators.py

**Tasks**:
1. Write tests for operator inheritance hierarchy
2. Move both operator base classes
3. Update theory operator imports
4. Test operator instantiation across theories

**Critical Testing**:
```bash
# Test each theory's operator definitions
for theory in logos exclusion imposition bimodal; do
  pytest src/model_checker/theory_lib/$theory/tests/test_*operators.py -v
done

# Test complex operator compositions
./dev_cli.py src/model_checker/theory_lib/logos/subtheories/*/examples.py
```

### Phase 3.5: Move OperatorCollection (Day 5)

**Component**: OperatorCollection class
**Target**: syntactic/collection.py

**Tasks**:
1. Write tests for registry functionality
2. Move OperatorCollection with all registry methods
3. Update theory collection usage
4. Test operator registration and lookup

**Testing Focus**:
- Operator registration mechanisms
- Lookup and retrieval accuracy
- Type checking and validation
- Uniqueness enforcement

### Phase 3.6: Move Syntax Class (Day 6)

**Component**: Syntax class
**Target**: syntactic/syntax.py

**Tasks**:
1. Write tests for argument processing
2. Move Syntax orchestration class
3. Update main import paths (critical!)
4. Test premise/conclusion handling

**Critical Testing**:
```bash
# Test main Syntax import (used everywhere)
from model_checker import Syntax  # Must work

# Test all examples still work
./run_tests.py --examples

# Test complex argument processing
./dev_cli.py -p src/model_checker/theory_lib/*/examples.py
```

### Phase 3.7: Cleanup and Validation (Day 7)

**Tasks**:
1. Remove old code from syntactic.py
2. Ensure __init__.py exports all classes correctly
3. Update documentation
4. Run comprehensive validation

**Final Validation**:
```bash
# Full test suite
./run_tests.py --unit --examples --package

# All theory operator tests
for theory in logos exclusion imposition bimodal; do
  pytest src/model_checker/theory_lib/$theory/tests/test_*operators.py -v
done

# Complex parsing validation
for subtheory in counterfactual constitutive extensional modal relevance; do
  ./dev_cli.py src/model_checker/theory_lib/logos/subtheories/$subtheory/examples.py
done
```

## Testing Protocols

### Dual Testing Methodology

Each refactoring step MUST use BOTH testing methods:

#### Method 1: Test-Driven Development
```bash
# Before moving each component
pytest src/model_checker/syntactic/tests/test_<component>.py -v

# After moving
./run_tests.py --package --components syntactic

# Full regression
./run_tests.py --unit --package
```

#### Method 2: CLI Validation (Critical for Operators)
```bash
# Test ALL theories after each change
for theory in logos exclusion imposition bimodal; do
  ./dev_cli.py src/model_checker/theory_lib/$theory/examples.py > \
    current/${theory}_syntactic.txt 2>&1
  diff -u baseline/${theory}_operators.txt current/${theory}_syntactic.txt
done

# Test complex operator parsing
for subtheory in counterfactual constitutive extensional modal relevance; do
  ./dev_cli.py src/model_checker/theory_lib/logos/subtheories/$subtheory/examples.py > \
    current/${subtheory}_syntactic.txt 2>&1
done

# Check for any parsing errors
grep -E "WARNING|Error|ParseError|SyntaxError|AttributeError" current/*.txt
```

### Regression Criteria

1. **No parsing errors** - All formulas parse correctly
2. **Operator functionality preserved** - All theory operators work
3. **Import compatibility** - All existing imports continue working
4. **No semantic binding issues** - Formula evaluation unchanged
5. **Performance maintained** - No significant slowdown in parsing

## Success Criteria

1. **Code Organization**
   - syntactic.py reduced to < 100 lines (imports only)
   - Each module < 300 lines
   - Clear separation of concerns

2. **Testing**
   - 100% test coverage for moved components
   - All existing operator tests pass
   - No CLI regressions

3. **Documentation**
   - Comprehensive README.md
   - Each module documented
   - Migration patterns documented

4. **Import Compatibility**
   - All existing imports work
   - Main imports (from model_checker import Syntax) preserved
   - No circular dependencies

## Risk Mitigation

1. **Operator Hierarchy Issues**
   - Test inheritance chain thoroughly
   - Verify abstract methods properly implemented
   - Check operator instantiation patterns

2. **Parser Integration**
   - Validate parse_expression integration
   - Test complex formula edge cases
   - Check error handling preservation

3. **Theory Integration**
   - Test every theory's operator definitions
   - Verify OperatorCollection functionality
   - Check theory-specific operator requirements

4. **Import Breakage**
   - Use __init__.py for compatibility
   - Test all dependent theory files
   - Provide clear migration path

## Timeline

- **Day 1**: Setup and baseline
- **Day 2**: Move atoms and utilities  
- **Day 3**: Move Sentence class
- **Day 4**: Move Operator classes (HIGH RISK)
- **Day 5**: Move OperatorCollection (HIGH RISK)
- **Day 6**: Move Syntax class (HIGH RISK)
- **Day 7**: Cleanup and validation

**Total**: 7 days with buffer for operator integration issues

## Next Steps

1. Review and approve this plan
2. Begin Phase 3.1 baseline capture
3. Create test infrastructure
4. Start incremental migration

## References

- [008_v1_release_preparation.md](008_v1_release_preparation.md) - Main refactoring plan
- [010_model_py_removal_and_polish.md](010_model_py_removal_and_polish.md) - Model.py success pattern
- [012_utils_refactoring_plan.md](012_utils_refactoring_plan.md) - Utils.py lessons learned
- [findings/011_model_py_removal_success.md](../findings/011_model_py_removal_success.md) - Lessons learned