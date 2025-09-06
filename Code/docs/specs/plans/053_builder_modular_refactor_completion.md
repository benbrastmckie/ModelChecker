# Implementation Plan: Complete Builder Modular Refactor

**Date**: 2025-09-05  
**Author**: AI Assistant  
**Status**: Ready for Review - REVISED with detailed implementation  
**Priority**: HIGH - Complete modular architecture for v1 stability  
**Related**: [028_builder_v1_modular_refactor.md](028_builder_v1_modular_refactor.md), [029_builder_test_refactor.md](029_builder_test_refactor.md), [052_builder_tests_cleanup_manual_testing.md](052_builder_tests_cleanup_manual_testing.md)  
**Focus**: Complete component extraction from BuildModule, verify with dual testing strategy

## Specification Validation

**Verification Checklist**:
- ✅ Clear problem statement (BuildModule still contains business logic that belongs in components)
- ✅ Detailed implementation phases (5 phases with specific code movements)
- ✅ Success criteria (all tests pass, manual tests work, clean architecture)
- ✅ Testing strategy (automated tests + manual verification per IMPLEMENT.md)
- ✅ NO BACKWARD COMPATIBILITY (following CLAUDE.md principles)
- ✅ Detailed code analysis showing exactly what moves where

## Executive Summary

Complete the modular refactor of the builder package. Research shows that ModelRunner, ModelComparison, and OperatorTranslation already exist but BuildModule still contains significant business logic that should be moved to these components.

**Current State Analysis**:
- `ModelRunner`, `ModelComparison`, `OperatorTranslation` classes exist but are incomplete
- `BuildModule` still contains:
  - `run_examples()` - 56 lines of execution logic (lines 274-345)
  - `_prompt_for_iterations()` - 23 lines (lines 131-153)  
  - `_capture_and_save_output()` - 71 lines (lines 156-227)
  - Delegation methods for backward compatibility (lines 228-273)
- Tests expect components to have more functionality than currently implemented

**Target State**:
- All business logic moved to appropriate components
- BuildModule reduced to ~50 lines (pure coordination)
- Components handle their own responsibilities completely
- NO delegation methods or backward compatibility
- All call sites updated to use components directly

## Current State Analysis

### Detailed Code Analysis

#### BuildModule (module.py - 345 lines total)

**Lines 1-125: Initialization**
- Component initialization already done (loader, runner, comparison, translation)
- Output manager setup
- Settings management

**Lines 131-153: `_prompt_for_iterations()`**
- User interaction logic that belongs in ModelRunner
- 23 lines of iteration handling
- Currently handles interactive mode prompting

**Lines 156-227: `_capture_and_save_output()`** 
- Output capture and formatting logic
- Should stay in BuildModule as it coordinates with OutputManager
- 71 lines of output handling

**Lines 228-273: Delegation Methods**
- `run_comparison()` - delegates to comparison (line 230)
- `translate()` - delegates to translation (line 240)  
- `translate_example()` - delegates to translation (line 250)
- MUST BE DELETED per no backward compatibility

**Lines 274-345: `run_examples()`**
- Main execution loop with Z3 isolation logic (lines 286-302)
- Critical Z3 context reset pattern (lines 294-302)
- Iteration through examples and theories
- Should move to ModelRunner
- 71 lines of core execution logic

#### ModelRunner (runner.py - current state)
- Has `process_example()` method (line 236) that's called by BuildModule
- Has `run_model_check()` (line 104) but not used by BuildModule
- Has `try_single_N()` (line 137) for comparison support
- Missing the main execution loop from BuildModule
- Missing iteration handling logic
- Already has Z3 isolation pattern in static method

#### ModelComparison (comparison.py - current state)  
- Has `compare_semantics()` (line 87) and related methods
- Has `run_comparison()` (line 136) - complete implementation
- Uses ProcessPoolExecutor for parallel execution
- Mostly complete, just needs BuildModule delegation removed

#### OperatorTranslation (translation.py - current state)
- Has `translate()` (line 11) and `translate_example()` (line 36)
- Complete implementation, no dependencies on BuildModule
- Just needs BuildModule delegation methods removed

### External Call Sites

**Main entry point** (`__main__.py`):
```python
# Line 265: Create BuildModule instance
module = BuildModule(module_flags)

# Line 269: Comparison mode
if module.general_settings["maximize"]:
    module.run_comparison()
    
# Line 272: Normal execution  
module.run_examples()
```

**Dev CLI** (`dev_cli.py`):
- Line 55: Calls main() from __main__.py
- No direct BuildModule usage

**Test files**: 
- `test_components.py` - expects component access patterns
- `test_loader.py` - tests ModuleLoader functionality
- `test_serialize.py` - tests serialization utilities

## Refactoring Philosophy (per CLAUDE.md)

### Core Principles Applied

1. **ALWAYS Break Compatibility**: 
   - NO delegation methods
   - NO optional parameters for transition
   - Update ALL call sites directly

2. **Simplify Aggressively**:
   - Remove all unnecessary abstractions
   - BuildModule becomes pure coordinator
   - Each component has single responsibility

3. **Remove Rather Than Deprecate**:
   - Delete old methods immediately
   - No transition period
   - Force clean migration

4. **Unified Interfaces**:
   - All components follow same initialization pattern
   - Consistent method signatures
   - Clear separation of concerns

## Implementation Plan

### Phase 1: NO NEW MODULES NEEDED

**Critical Finding**: ModelRunner, ModelComparison, and OperatorTranslation already exist!
- `runner.py` - exists with partial implementation
- `comparison.py` - exists with full implementation
- `translation.py` - exists with full implementation

**Actual Task**: Move missing methods from BuildModule to existing components

### Phase 1.5: Analyze Missing Functionality

**What's Missing from Components**:

#### ModelRunner needs:
1. **`run_examples()`** - Main execution loop from BuildModule (lines 274-345)
   - Critical Z3 context isolation logic (lines 294-302)
   - Example/theory iteration logic
   - Keyboard interrupt handling
   - Output finalization

2. **`_prompt_for_iterations()`** - Interactive iteration handling (lines 131-153)
   - User input processing
   - Validation and retry logic

#### ModelComparison:
- Already complete! Just needs BuildModule delegation removed

#### OperatorTranslation:
- Already complete! Just needs BuildModule delegation removed

### Phase 2: Extract Methods from BuildModule

**Objective**: Move methods from BuildModule to appropriate components

#### Task 2.1: Identify ACTUAL Methods to Move

**To ModelRunner**:
- `run_examples()` (lines 274-345) - Main execution loop
- `_prompt_for_iterations()` (lines 131-153) - Interactive mode handling

**To ModelComparison**:
- No methods to move - comparison.py already has run_comparison()

**To OperatorTranslation**:
- No methods to move - translation.py already has translate() methods

**KEEP in BuildModule**:
- `_capture_and_save_output()` - coordinates with OutputManager

#### Task 2.2: Extract Runner Methods

**Move `run_examples()` to ModelRunner:**
```python
def run_examples(self):
    """Process all examples with all theories."""
    # CRITICAL: Move lines 274-345 from BuildModule INCLUDING Z3 isolation
    # The Z3 context reset (lines 294-302) is ESSENTIAL:
    
    import gc
    import z3
    import sys
    
    try:
        for example_name, example_case in self.build_module.example_range.items():
            # Force garbage collection
            gc.collect()
            
            # CRITICAL Z3 CONTEXT RESET - DO NOT OMIT!
            if hasattr(z3, '_main_ctx'):
                z3._main_ctx = None
            
            gc.collect()
            
            for theory_name, semantic_theory in self.build_module.semantic_theories.items():
                # Make setting reset for each semantic_theory
                example_copy = list(example_case)
                example_copy[2] = example_case[2].copy()
                
                try:
                    self.process_example(example_name, example_copy, theory_name, semantic_theory)
                finally:
                    gc.collect()
                    
    except KeyboardInterrupt:
        print("\n\nExecution interrupted by user.")
        # Handle output finalization...
        sys.exit(1)
    
    # Finalize output if needed
    if self.build_module.output_manager.should_save():
        self.build_module.output_manager.finalize()
        # ... rest of output handling
```

**Move `_prompt_for_iterations()` to ModelRunner:**
```python
def prompt_for_iterations(self):
    """Prompt user for iterations."""
    # Move lines 131-153 from BuildModule
    # Make public (remove underscore)
```

#### Task 2.3: DELETE Delegation Methods from BuildModule

**Methods to DELETE completely**:
```python
# DELETE these delegation methods:
def run_comparison(self):
    """DELETE - callers use self.comparison.run_comparison()"""
    
def translate(self, example_case, dictionary):
    """DELETE - callers use self.translation.translate()"""
    
def translate_example(self, example_case, semantic_theories):
    """DELETE - callers use self.translation.translate_example()"""
```

### Phase 3: Update BuildModule and All Call Sites

**Objective**: Transform BuildModule into a pure coordinator and update ALL call sites

#### Task 3.1: Strip BuildModule to Coordinator Role

**BuildModule after refactor (target ~100 lines)**:
```python
class BuildModule:
    """Coordinator for model checking components.
    
    NO BACKWARD COMPATIBILITY - BuildModule only coordinates components.
    All functionality moved to dedicated components.
    """
    
    def __init__(self, module_flags):
        # Basic setup (lines 40-60)
        self.module_flags = module_flags
        self.module_path = self.module_flags.file_path
        self.module_name = os.path.splitext(os.path.basename(self.module_path))[0]
        
        # Initialize components (lines 61-80)
        self.loader = ModuleLoader(self.module_name, self.module_path)
        self.runner = ModelRunner(self)
        self.comparison = ModelComparison(self)
        self.translation = OperatorTranslation()
        
        # Load module and settings (lines 81-105)
        self.loaded_module = self.loader.load_module()
        self.semantic_theories = self.loader.load_semantic_theories(self.loaded_module)
        self.example_range = self.loader.load_examples(self.loaded_module)
        self.general_settings = self.loader.extract_settings(self.loaded_module, self.module_flags)
        
        # Output management (lines 106-120)
        self.output_manager = OutputManager(self.module_flags, self.module_name)
        if self.module_flags.interactive:
            self.interactive_manager = InteractiveSaveManager(self.output_manager)
        else:
            self.interactive_manager = None
    
    def _capture_and_save_output(self, example, example_name, theory_name, model_num=None):
        """Coordinate output capture with OutputManager."""
        # Keep this method - it coordinates components
        # Lines 156-227 stay here
```

#### Task 3.2: Update ALL Call Sites

**Main entry point (`__main__.py`):**
```python
# Line 269 - OLD:
module.run_comparison()
# NEW:
module.comparison.run_comparison()

# Line 272 - OLD:
module.run_examples()
# NEW:
module.runner.run_examples()
```

**Within ModelRunner.process_example():**
```python
# Line 256 - OLD:
example_case = self.build_module.translation.translate(example_case, dictionary)
# KEEP AS IS - already using component
```

**Within ModelComparison.run_comparison():**
```python
# Line 162 - OLD:
translated_case = self.build_module.translation.translate(example_case, dictionary)
# KEEP AS IS - already using component
```

#### Task 3.3: Delete run_examples() and run_comparison() from BuildModule

**Current BuildModule methods to DELETE**:
- `run_examples()` (lines 274-345) - moved to ModelRunner
- `run_comparison()` (if exists) - callers use component directly
- `translate()` (if exists) - callers use component directly
- `translate_example()` (if exists) - callers use component directly
- `_prompt_for_iterations()` (lines 131-153) - moved to ModelRunner

**BuildModule should ONLY have**:
- `__init__()` - initialization
- `_capture_and_save_output()` - output coordination
- Component references and settings

### Phase 4: Fix Tests and Update All Dependencies

**Objective**: Ensure all tests pass and update all code that depends on BuildModule

#### Task 4.1: Update Test Files
```python
# Update all test files to use components directly
# Example fixes:

# OLD test code:
result = build_module.run_model_check(...)

# NEW test code:
result = build_module.runner.run_model_check(...)

# NO delegation methods - direct component access only
```

#### Task 4.2: Update Theory Library Integration
```bash
# Find all theory library code that uses BuildModule
grep -r "BuildModule" src/model_checker/theory_lib/

# Update any found usages to component-based approach
```

#### Task 4.3: Run Automated Tests
```bash
# Run all builder tests - expect failures initially
./run_tests.py --package builder

# Fix each failure by updating to new API
# NO adding compatibility methods - update call sites

# Run specific test files during fixes
pytest src/model_checker/builder/tests/test_components.py -v
pytest src/model_checker/builder/tests/test_component_integration.py -v
pytest src/model_checker/builder/tests/test_error_propagation.py -v

# Check coverage after fixes
pytest --cov=model_checker.builder --cov-report=term-missing
```

#### Task 4.3: Run Manual Tests

Follow MANUAL_TESTING.md protocol:

```bash
# Test theory library examples
./dev_cli.py src/model_checker/theory_lib/logos/examples.py
./dev_cli.py src/model_checker/theory_lib/logos/subtheories/modal/examples.py
./dev_cli.py src/model_checker/theory_lib/exclusion/examples.py
./dev_cli.py src/model_checker/theory_lib/imposition/examples.py
./dev_cli.py src/model_checker/theory_lib/bimodal/examples.py

# Test iteration mode
./dev_cli.py -i src/model_checker/theory_lib/logos/examples.py
# Enter: 5

# Test comparison mode
./dev_cli.py -c src/model_checker/theory_lib/logos/examples.py

# Test generated projects
./model-checker
# Choose logos, create project
./dev_cli.py project_*/examples.py
```

### Phase 5: Clean Up and Document

**Objective**: Remove ALL old code, update documentation

#### Task 5.1: Strip BuildModule to Minimum
```python
# BuildModule should ONLY have:
# - __init__ (component initialization)
# - run() (coordination logic)
# - Attributes needed by components

# DELETE all methods that were moved
# NO delegation methods
# NO compatibility layers
```

#### Task 5.2: Update Documentation
- Update BuildModule docstring to reflect coordinator role
- Document component responsibilities clearly
- Update README files with new architecture
- Add clear migration guide for users

#### Task 5.3: Performance Verification
```bash
# Run performance comparison
time ./dev_cli.py src/model_checker/theory_lib/logos/examples.py

# Compare with old version timings
# Should be same or better performance
```

## Testing Strategy (Following IMPLEMENT.md)

### Dual Testing Methodology

Per IMPLEMENT.md requirements, use BOTH testing methods:

#### Method 1: Test-Driven Development with Test Runner

```bash
# Write tests FIRST for each component
# Then implement to pass tests
./run_tests.py --package builder -v

# Full test suite after each phase
./run_tests.py --all
```

#### Method 2: Direct CLI Testing with dev_cli.py

```bash
# Test individual theories
./dev_cli.py src/model_checker/theory_lib/logos/examples.py
./dev_cli.py src/model_checker/theory_lib/bimodal/examples.py

# CRITICAL: Test with iterations for regression detection
./dev_cli.py src/model_checker/theory_lib/logos/examples.py
# Run same command 3 times to catch iterator issues

# Systematic testing of all theories
for theory in logos bimodal exclusion imposition; do
    echo "Testing $theory..."
    ./dev_cli.py src/model_checker/theory_lib/$theory/examples.py
done
```

### Success Criteria
- Method 1: All unit tests passing, no regressions
- Method 2: No AttributeErrors or warnings in output
- Both Methods: Consistent results before/after changes
- No Z3 casting errors

### Test Execution Order

1. **Before Each Change**:
   - Run affected unit tests
   - Quick manual test of specific feature

2. **After Each Phase**:
   - Run all builder tests
   - Run integration tests
   - Quick manual smoke test

3. **After Complete Implementation**:
   - Full test suite
   - Complete manual testing protocol
   - Performance comparison

## Success Metrics

1. **All Tests Pass (Both Methods)**:
   - 137+ builder tests passing (Method 1)
   - No AttributeErrors in dev_cli.py (Method 2)
   - No regression in other packages
   - Coverage ≥80%

2. **Clean Architecture Achieved**:
   - NO backward compatibility code
   - Clear separation of concerns
   - Components work independently
   - BuildModule is pure coordinator

3. **All Call Sites Updated**:
   - No remaining calls to old BuildModule methods
   - All tests updated to new API
   - Theory library integration updated
   - Documentation reflects new structure

4. **Performance Maintained**:
   - No degradation (per IMPLEMENT.md)
   - Memory usage similar or better

## Risk Mitigation

### Risks and Mitigations

1. **Risk**: Breaking Z3 isolation causing timeouts
   - **Mitigation**: MUST preserve exact Z3 context reset logic
   - **Mitigation**: Test with multiple examples in sequence
   - **Mitigation**: Manual test protocol includes iteration testing

2. **Risk**: Breaking existing functionality
   - **Mitigation**: Update ALL call sites (no compatibility layer to miss)
   - **Mitigation**: Dual testing methodology catches issues

3. **Risk**: Circular dependencies between components
   - **Mitigation**: Components only reference BuildModule, not each other
   - **Mitigation**: Clear dependency direction enforced

4. **Risk**: Missing call sites during update
   - **Mitigation**: Systematic grep searches for all usages
   - **Mitigation**: Tests will fail if any missed
   
5. **Risk**: Performance regression
   - **Mitigation**: Profile before/after per IMPLEMENT.md
   - **Mitigation**: Fail-fast on performance degradation

## Implementation Order (REVISED)

1. **Extract methods to ModelRunner** (45 min)
   - Move `run_examples()` with Z3 isolation logic
   - Move `_prompt_for_iterations()` (make public)
   - Update all internal references
   - Test basic functionality

2. **Delete delegation methods** (15 min)
   - Remove `run_comparison()` if exists
   - Remove `translate()` if exists
   - Remove `translate_example()` if exists
   - Verify no backward compatibility code remains

3. **Update call sites** (30 min)
   - Update `__main__.py` lines 269 and 272
   - Search for any other BuildModule method calls
   - Update all to use components directly

4. **Fix failing tests** (1 hour)
   - Run `./run_tests.py --package builder`
   - Fix test_components.py (expect 15 failures)
   - Update test expectations for new API
   - Verify all tests pass

5. **Manual testing protocol** (30 min)
   - Test all theory libraries with dev_cli.py
   - Test iteration mode (-i flag)
   - Test comparison mode (-m flag)
   - Verify no AttributeErrors

6. **Cleanup and documentation** (15 min)
   - Verify BuildModule is ~100 lines
   - Update component docstrings
   - Update README if needed

**Total Estimate**: 3 hours (faster because components already exist!)

## Appendix: Component Interaction Diagram

```
┌─────────────────┐
│   dev_cli.py    │
└────────┬────────┘
         │
┌────────▼────────┐
│  __main__.py    │
└────────┬────────┘
         │
┌────────▼────────┐
│   BuildModule   │ ← Pure coordinator (~100 lines)
├─────────────────┤
│ - module_flags  │
│ - settings      │
│ - components:   │
│   ├─ loader     │──────┐
│   ├─ runner     │──────┤  Components reference parent
│   ├─ comparison │──────┤  for settings/output access
│   └─ translation│──────┘  
│ - output_manager│
│ - _capture_and_save_output()│
└─────────────────┘

Component responsibilities:
- loader: Module discovery and loading
- runner: Model checking execution + run_examples()
- comparison: Multi-theory comparison + run_comparison()
- translation: Operator conversion

Call flow:
__main__.py → module.runner.run_examples()
          → module.comparison.run_comparison()

NO delegation methods in BuildModule
ALL execution in components
```

## Appendix: Migration Checklist

### Phase 1: Component Creation
- [ ] Create runner.py with ModelRunner class
- [ ] Create comparison.py with ModelComparison class  
- [ ] Create translation.py with OperatorTranslation class

### Phase 2: Method Extraction
- [ ] Move runner methods from BuildModule
- [ ] Move comparison methods from BuildModule
- [ ] Move translation methods from BuildModule

### Phase 3: BuildModule Update
- [ ] Strip BuildModule to coordinator only
- [ ] Add component initialization
- [ ] Update run() method
- [ ] Find ALL call sites with grep
- [ ] Update ALL call sites to use components

### Phase 4: Test Updates
- [ ] Update all test files for new API
- [ ] Fix theory library integration
- [ ] Run Method 1 tests (test runner)
- [ ] Run Method 2 tests (dev_cli.py iterations)
- [ ] Verify no regressions

### Phase 5: Cleanup
- [ ] DELETE `run_examples()` from BuildModule
- [ ] DELETE `_prompt_for_iterations()` from BuildModule  
- [ ] DELETE any delegation methods (run_comparison, translate, etc)
- [ ] Verify BuildModule is ~100 lines
- [ ] NO backward compatibility code remains
- [ ] Update builder/README.md
- [ ] Performance verification

### Critical Implementation Details

#### Z3 Context Isolation Pattern
**MUST PRESERVE** the Z3 context reset logic from BuildModule.run_examples():
```python
# Lines 294-302 are CRITICAL for proper Z3 state isolation
import z3
if hasattr(z3, '_main_ctx'):
    z3._main_ctx = None
```

This prevents state leakage between examples that causes timeout issues.

#### Method Signature Updates
When moving methods to components:
1. `self.example_range` → `self.build_module.example_range`
2. `self.semantic_theories` → `self.build_module.semantic_theories`
3. `self.output_manager` → `self.build_module.output_manager`
4. `self.module_flags` → `self.build_module.module_flags`

#### Test Update Pattern
```python
# OLD pattern in tests:
assert hasattr(build_module, 'run_examples')
build_module.run_examples()

# NEW pattern:
assert hasattr(build_module.runner, 'run_examples')
build_module.runner.run_examples()
```

### Debugging Philosophy Checklist (per IMPLEMENT.md)
- [ ] Prefer deterministic failures
- [ ] Deep root cause analysis for any errors
- [ ] Implement systematic solutions
- [ ] Remove all cruft discovered
- [ ] NO backward compatibility code

---

## Summary of Key Changes

### What's Actually Happening
1. **Components Already Exist** - No need to create new files!
   - ModelRunner, ModelComparison, OperatorTranslation are already implemented
   - Just need to move missing methods

2. **Critical Methods to Move**:
   - `run_examples()` → ModelRunner (with Z3 isolation logic!)
   - `_prompt_for_iterations()` → ModelRunner (make public)

3. **Methods to DELETE from BuildModule**:
   - All delegation methods (if any exist)
   - The moved methods above
   - NO backward compatibility

4. **Call Sites to Update**:
   - `__main__.py` line 269: `module.run_comparison()` → `module.comparison.run_comparison()`
   - `__main__.py` line 272: `module.run_examples()` → `module.runner.run_examples()`

5. **Expected Test Failures**:
   - ~15 tests in test_components.py expect the refactored API
   - These will pass once implementation is complete

**Ready for Implementation**: This revised plan with detailed code analysis provides clear, actionable steps to complete the builder refactor in ~3 hours instead of 5.