# Implementation Plan: Models Subpackage Refactoring

## Overview

This plan implements the refactoring of the models/ subpackage as identified in the comprehensive subpackage analysis. The main target is splitting the monolithic `structure.py` (788 lines) into focused, single-responsibility modules following the revised IMPLEMENT.md process.

## Current State Analysis

### models/structure.py Issues

The ModelDefaults class in `structure.py` currently handles:
1. Z3 solver management and constraint solving
2. Result processing and interpretation
3. 8+ display/printing methods
4. Model comparison and differences calculation
5. Test file generation
6. ANSI color codes and formatting constants

This violates the Single Responsibility Principle and makes the code difficult to maintain and test.

### Code Duplication Issues

- Display formatting logic duplicated with builder/module.py
- ANSI color codes hardcoded in multiple places
- Similar error handling patterns throughout

## Proposed Structure

```
models/
├── __init__.py          # Package exports
├── README.md            # Updated documentation
├── semantic.py          # SemanticDefaults (existing)
├── proposition.py       # PropositionDefaults (existing)
├── constraints.py       # ModelConstraints (existing)
├── core.py             # Core ModelDefaults functionality
├── solver.py           # Z3 solver setup and management
├── display.py          # All printing/display methods
├── comparison.py       # Model comparison logic
├── constants.py        # ANSI colors and display constants
└── tests/
    ├── test_core.py
    ├── test_solver.py
    ├── test_display.py
    ├── test_comparison.py
    └── test_constants.py
```

## Implementation Phases

### Phase 1: Research and Design (Complete)

**Status**: ✅ Complete

- Research report completed in 012_comprehensive_subpackage_analysis.md
- Current structure analyzed with 788-line structure.py identified as priority
- Dependencies mapped across codebase

### Phase 2: Setup and Baseline

**Tasks**:

1. **Capture Baseline** (Following Testing Protocol from IMPLEMENT.md)
   ```bash
   # Create baseline directory
   mkdir -p docs/specs/baselines/models_refactor
   
   # Capture current functionality
   ./dev_cli.py src/model_checker/theory_lib/logos/examples.py > docs/specs/baselines/models_refactor/logos_baseline.txt 2>&1
   ./dev_cli.py src/model_checker/theory_lib/bimodal/examples.py > docs/specs/baselines/models_refactor/bimodal_baseline.txt 2>&1
   ./dev_cli.py src/model_checker/theory_lib/exclusion/examples.py > docs/specs/baselines/models_refactor/exclusion_baseline.txt 2>&1
   ./dev_cli.py src/model_checker/theory_lib/imposition/examples.py > docs/specs/baselines/models_refactor/imposition_baseline.txt 2>&1
   
   # Test with iterations (critical for solver functionality)
   for i in 1 2 3; do
     ./dev_cli.py -i $i src/model_checker/theory_lib/logos/examples.py > docs/specs/baselines/models_refactor/logos_iter${i}_baseline.txt 2>&1
   done
   
   # Test display functionality
   ./dev_cli.py -p src/model_checker/theory_lib/logos/examples.py > docs/specs/baselines/models_refactor/display_baseline.txt 2>&1
   
   # Run full test suite
   ./run_tests.py --all > docs/specs/baselines/models_refactor/tests_baseline.txt 2>&1
   ```

2. **Map Dependencies**
   ```bash
   # Find all imports of ModelDefaults
   grep -r "from.*structure import" src/ --include="*.py"
   grep -r "ModelDefaults" src/ --include="*.py" | grep -v "structure.py"
   ```

3. **Create Test Infrastructure** (Following TDD from Testing Protocol)
   - Write comprehensive tests for each planned module BEFORE extraction
   - Focus on interface contracts, not implementation details

**Success Criteria**:
- [ ] All baselines captured and stored
- [ ] Dependency map documented
- [ ] Test files created for each planned module
- [ ] No regression in baseline tests

### Phase 3: Extract Constants Module

**Objective**: Extract all ANSI codes and display constants to eliminate duplication

**Tasks**:

1. **Write Tests First** (TDD)
   ```python
   # src/model_checker/models/tests/test_constants.py
   def test_ansi_colors_available():
       from model_checker.models.constants import ANSI_COLORS
       assert 'GREEN' in ANSI_COLORS
       assert 'RED' in ANSI_COLORS
       assert 'RESET' in ANSI_COLORS
   
   def test_display_constants():
       from model_checker.models.constants import DISPLAY_CONSTANTS
       assert 'HEADER_WIDTH' in DISPLAY_CONSTANTS
       assert 'SEPARATOR' in DISPLAY_CONSTANTS
   ```

2. **Create constants.py**
   - Extract all ANSI color definitions
   - Extract display width constants
   - Extract separator patterns
   - Create enums where appropriate

3. **Update structure.py**
   - Import from constants module
   - Remove local definitions
   - Ensure all references updated

**Testing Protocol** (Both Methods):
- Method 1: `./run_tests.py --package --components models`
- Method 2: `./dev_cli.py -p src/model_checker/theory_lib/logos/examples.py`

**Success Criteria**:
- [ ] All color codes in one place
- [ ] No hardcoded ANSI strings in structure.py
- [ ] Display output unchanged from baseline

### Phase 4: Extract Solver Module

**Objective**: Separate Z3 solver management from core functionality

**Tasks**:

1. **Write Tests First** (TDD)
   ```python
   # src/model_checker/models/tests/test_solver.py
   def test_solver_initialization():
       from model_checker.models.solver import ModelSolver
       solver = ModelSolver(context=z3.Context())
       assert solver.solver is not None
   
   def test_constraint_solving():
       # Test solve() method contract
       # Test re_solve() method contract
       # Test extract_assignment()
   ```

2. **Create solver.py**
   - Move `solve()` method
   - Move `re_solve()` method
   - Move `extract_assignment()` method
   - Move all Z3-specific helper methods
   - Keep clean interface for ModelDefaults

3. **Update structure.py**
   - Create ModelSolver instance
   - Delegate solver operations
   - Maintain existing API

**Debugging Philosophy Application**:
- If Z3 casting errors occur, apply explicit evaluation pattern
- Document any Z3-specific workarounds
- Ensure solver isolation is maintained

**Success Criteria**:
- [ ] Clean separation of solver logic
- [ ] All solving tests pass
- [ ] Iterator functionality preserved (critical!)
- [ ] No Z3 casting errors

### Phase 5: Extract Display Module

**Objective**: Consolidate all printing and display methods

**Tasks**:

1. **Write Tests First** (TDD)
   ```python
   # src/model_checker/models/tests/test_display.py
   def test_print_info():
       # Test various display formats
       # Test ANSI color application
       # Test with/without color settings
   ```

2. **Create display.py**
   - Move all `print_*` methods:
     - `print_info()`
     - `print_raw()`
     - `print_model_flat()`
     - `print_propositional_model_flat()`
     - `print_models_side_by_side()`
     - `print_models_as_text()`
     - `_print_details()`
     - `_print_states()`
   - Create DisplayFormatter class
   - Use constants from constants.py

3. **Update structure.py**
   - Create DisplayFormatter instance
   - Delegate display operations
   - Keep interface unchanged

**Success Criteria**:
- [ ] All display methods in one module
- [ ] Output identical to baseline
- [ ] Clean interface for display operations

### Phase 6: Extract Comparison Module

**Objective**: Separate model comparison logic

**Tasks**:

1. **Write Tests First** (TDD)
   ```python
   # src/model_checker/models/tests/test_comparison.py
   def test_model_difference():
       # Test difference calculation
       # Test set operations
       # Test comparison display
   ```

2. **Create comparison.py**
   - Move `find_model_differences()` method
   - Move `find_contingent_truths()` method
   - Move comparison-related helpers
   - Create ModelComparator class

3. **Update structure.py**
   - Use ModelComparator for comparisons
   - Maintain existing API

**Success Criteria**:
- [ ] Clean separation of comparison logic
- [ ] All comparison tests pass
- [ ] No functional changes

### Phase 7: Refactor Core Module

**Objective**: Clean up remaining ModelDefaults to focus on core functionality

**Tasks**:

1. **Refactor structure.py to core.py**
   - Rename file to better reflect content
   - Use composition with extracted modules:
     - self.solver = ModelSolver()
     - self.display = DisplayFormatter()
     - self.comparator = ModelComparator()
   - Focus on core model state and coordination

2. **Update all imports**
   ```bash
   # Update imports from structure to core
   find src/ -name "*.py" -exec sed -i 's/from \.structure import/from \.core import/g' {} \;
   ```

3. **Clean up interfaces**
   - Ensure all public methods maintained
   - Document any internal API changes
   - Remove any remaining duplication

**Success Criteria**:
- [ ] ModelDefaults under 200 lines
- [ ] Clear single responsibility
- [ ] All tests pass

### Phase 8: Integration and Validation

**Tasks**:

1. **Run Full Validation Suite** (Both Testing Methods)
   ```bash
   # Method 1: Test Runner
   ./run_tests.py --all --verbose
   
   # Method 2: CLI Testing
   for theory in logos bimodal exclusion imposition; do
     for i in 1 2 3; do
       ./dev_cli.py -i $i src/model_checker/theory_lib/$theory/examples.py > current/${theory}_iter${i}.txt 2>&1
     done
   done
   
   # Compare against baselines
   for file in current/*.txt; do
     base=$(basename $file .txt)
     diff -u docs/specs/baselines/models_refactor/${base}_baseline.txt $file
   done
   ```

2. **Performance Validation**
   ```bash
   # Benchmark before/after
   time ./run_tests.py --examples
   ```

3. **Update Documentation**
   - Update models/README.md with new structure
   - Document module responsibilities
   - Update any API documentation

**Success Criteria**:
- [ ] No regression from baseline
- [ ] Performance within 5% of original
- [ ] All documentation updated
- [ ] Zero warnings or errors

## Risk Mitigation

### High Risk Areas

1. **Solver Extraction**: Core to all functionality
   - Mitigation: Extensive testing with iterations
   - Fallback: Can revert solver changes independently

2. **Import Updates**: May miss some imports
   - Mitigation: Systematic grep and sed
   - Validation: Full test suite catches issues

3. **Iterator Regression**: Previous issues with iterator
   - Mitigation: Specific iteration testing in baseline
   - Focus: Preserve exact solver behavior

### Debugging Philosophy Application

Following IMPLEMENT.md debugging principles:
- Each extraction improves code quality
- Errors are opportunities to enhance architecture
- No quick patches - systematic solutions only
- Document all Z3-specific workarounds

## Timeline Estimate

- Phase 2 (Setup): 0.5 days
- Phase 3 (Constants): 0.5 days
- Phase 4 (Solver): 1 day
- Phase 5 (Display): 1 day
- Phase 6 (Comparison): 0.5 days
- Phase 7 (Core refactor): 0.5 days
- Phase 8 (Validation): 0.5 days

**Total: 4.5 days**

## Success Metrics

1. **Code Quality**:
   - No file exceeds 300 lines
   - Each module has single responsibility
   - No code duplication

2. **Functionality**:
   - All tests pass
   - No regression from baseline
   - Iterator works correctly

3. **Performance**:
   - No significant slowdown
   - Memory usage unchanged

4. **Maintainability**:
   - Clear module boundaries
   - Comprehensive test coverage
   - Updated documentation

## Next Steps

1. Complete Phase 2 baseline capture
2. Begin TDD test creation for constants module
3. Execute phases sequentially with validation
4. Document findings and any architectural discoveries

---

*This plan follows the revised IMPLEMENT.md process with emphasis on Testing Protocol, Debugging Philosophy, and Implementation Process*