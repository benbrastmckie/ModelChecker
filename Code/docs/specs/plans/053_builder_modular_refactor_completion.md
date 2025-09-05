# Implementation Plan: Complete Builder Modular Refactor

**Date**: 2025-09-05  
**Author**: AI Assistant  
**Status**: Ready for Review  
**Priority**: HIGH - Complete modular architecture for v1 stability  
**Related**: [028_builder_v1_modular_refactor.md](028_builder_v1_modular_refactor.md), [029_builder_test_refactor.md](029_builder_test_refactor.md), [052_builder_tests_cleanup_manual_testing.md](052_builder_tests_cleanup_manual_testing.md)  
**Focus**: Extract components from BuildModule, verify with dual testing strategy

## Specification Validation

**Verification Checklist**:
- ✅ Clear problem statement (monolithic BuildModule needs component extraction)
- ✅ Detailed implementation phases (5 phases with specific tasks)
- ✅ Success criteria (all tests pass, manual tests work, clean architecture)
- ✅ Testing strategy (automated tests + manual verification)
- ✅ NO BACKWARD COMPATIBILITY (following CLAUDE.md principles)

## Executive Summary

Complete the modular refactor of the builder package by extracting runner, comparison, and translation functionality into separate components. This follows up on spec 028 which established the architecture, and spec 052 which prepared comprehensive tests.

**Current State**:
- Monolithic `BuildModule` class with all functionality
- Tests written for future modular architecture (TDD approach)
- Manual testing protocol established

**Target State**:
- Separate `ModelRunner`, `ModelComparison`, `OperatorTranslation` components
- Clean architecture with BuildModule as coordinator only
- All tests passing (unit, integration, manual)
- NO backward compatibility - update all call sites

## Current State Analysis

### BuildModule Current Responsibilities

1. **Module Loading** - Already extracted to `loader.py` ✅
2. **Validation** - Already extracted to `validation.py` ✅
3. **Project Management** - Already extracted to `project.py` ✅
4. **Example Building** - Already extracted to `example.py` ✅
5. **Model Running** - Still in BuildModule ❌
6. **Comparison** - Still in BuildModule ❌
7. **Translation** - Still in BuildModule ❌
8. **Serialization** - Already extracted to `serialize.py` ✅
9. **Z3 Utilities** - Already extracted to `z3_utils.py` ✅

### Test Suite Status

From spec 052 implementation:
- `test_components.py` - Tests for future components (15 failures expected)
- `test_component_integration.py` - Integration tests ready
- `test_error_propagation.py` - Error handling tests ready
- `fixtures.py` - Comprehensive test utilities
- Manual testing protocol documented

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

### Phase 1: Create Component Modules

**Objective**: Create the three new component modules with proper structure

#### Task 1.1: Create runner.py
```python
# src/model_checker/builder/runner.py
"""Model runner component for executing model checking tasks."""

from typing import Dict, List, Tuple, Any, Optional
import z3
from ..defaults import SemanticDefaults


class ModelRunner:
    """Handles model checking execution and iteration."""
    
    def __init__(self, build_module):
        """Initialize with reference to parent BuildModule.
        
        Args:
            build_module: Parent BuildModule instance for accessing other components
        """
        self.build_module = build_module
    
    def run_model_check(self, example_name: str, example_case: List,
                       semantic_theory: SemanticDefaults, 
                       build_module, flags) -> Dict[str, Any]:
        """Run model checking for a single example."""
        # Implementation moved from BuildModule
        pass
    
    def try_single_N(self, example_name: str, premises: List[str],
                     conclusions: List[str], N: int,
                     semantic_theory: SemanticDefaults,
                     general_settings: Dict, flags) -> Tuple[bool, Optional[Any]]:
        """Try model checking with specific N value."""
        # Implementation moved from BuildModule
        pass
    
    def process_example(self, example_name: str, example_case: List,
                       semantic_theory: SemanticDefaults,
                       build_module, flags) -> None:
        """Process a single example."""
        # Implementation moved from BuildModule
        pass
    
    def process_iterations(self, example_name: str, valid: bool,
                          model: Any, settings: Dict, flags) -> None:
        """Handle iteration requests from user."""
        # Implementation moved from BuildModule
        pass
```

#### Task 1.2: Create comparison.py
```python
# src/model_checker/builder/comparison.py
"""Model comparison component for comparing semantic theories."""

from typing import Dict, Any
import multiprocessing


class ModelComparison:
    """Handles comparison of multiple semantic theories."""
    
    def __init__(self, build_module):
        """Initialize with reference to parent BuildModule."""
        self.build_module = build_module
    
    def compare_semantics(self, example_name: str, example_case: List,
                         semantic_theories: Dict, flags) -> Dict[str, Any]:
        """Compare example across multiple semantic theories."""
        # Implementation moved from BuildModule
        pass
    
    def run_comparison(self, module: Any, semantic_theories: Dict,
                      cpus: int = 1) -> None:
        """Run full comparison across all examples."""
        # Implementation moved from BuildModule
        pass
    
    def _find_max_N(self, example_case: List) -> int:
        """Find maximum N value for comparison."""
        # Implementation moved from BuildModule
        pass
    
    def _compare_single_example(self, theory_name: str, theory: Any,
                               example_name: str, example_case: List,
                               flags) -> Tuple[str, Dict]:
        """Compare single example with one theory."""
        # Implementation moved from BuildModule
        pass
```

#### Task 1.3: Create translation.py
```python
# src/model_checker/builder/translation.py
"""Operator translation component for formula conversion."""

from typing import Dict, List, Any


class OperatorTranslation:
    """Handles translation of operators in formulas."""
    
    def __init__(self):
        """Initialize translation component."""
        pass
    
    def translate(self, example_case: List, dictionary: Dict[str, str]) -> List:
        """Translate operators in example case."""
        # Implementation moved from BuildModule
        pass
    
    def translate_formula(self, formula: str, dictionary: Dict[str, str]) -> str:
        """Translate operators in a single formula."""
        # Implementation moved from BuildModule
        pass
    
    def translate_example(self, example_name: str, example_case: List,
                         dictionary: Dict[str, str]) -> List:
        """Translate entire example with logging."""
        # Implementation moved from BuildModule
        pass
```

### Phase 2: Extract Methods from BuildModule

**Objective**: Move methods from BuildModule to appropriate components

#### Task 2.1: Identify Methods to Move

**To ModelRunner**:
- `run_model_check()`
- `try_single_N()` 
- `process_example()`
- `process_iterations()`
- `_extract_settings()`
- `_handle_user_iteration()`

**To ModelComparison**:
- `compare_semantics()`
- `run_comparison()`
- `_find_max_N()`
- `_compare_single_example()`
- `_process_comparison_results()`

**To OperatorTranslation**:
- `translate()`
- `translate_formula()`
- `translate_example()`
- `_replace_operators()`

#### Task 2.2: Extract Runner Methods

1. Copy methods to `runner.py` with proper imports
2. Update method signatures to use `self.build_module` for dependencies
3. Handle z3 context management properly
4. Ensure error handling preserved

#### Task 2.3: Extract Comparison Methods

1. Copy methods to `comparison.py`
2. Update multiprocessing logic if needed
3. Ensure proper serialization handling
4. Maintain backward compatibility

#### Task 2.4: Extract Translation Methods

1. Copy methods to `translation.py`
2. Simplify since no BuildModule dependency needed
3. Add proper validation

### Phase 3: Update BuildModule and All Call Sites

**Objective**: Transform BuildModule into a pure coordinator and update ALL call sites

#### Task 3.1: Strip BuildModule to Coordinator Role
```python
class BuildModule:
    """Coordinator for model checking components.
    
    NO BACKWARD COMPATIBILITY - BuildModule only coordinates components.
    All functionality moved to dedicated components.
    """
    
    def __init__(self, module_flags):
        self.module_flags = module_flags
        self.module_path = self.module_flags.file_path
        self.module_name = os.path.splitext(os.path.basename(self.module_path))[0]
        
        # Initialize components
        self.loader = ModuleLoader(self.module_name, self.module_path)
        self.runner = ModelRunner(self)
        self.comparison = ModelComparison(self)
        self.translation = OperatorTranslation()
        
        # Load module and expose needed attributes
        self.loaded_module = self.loader.load_module()
        self.semantic_theories = self.loaded_module.semantic_theories
        self.example_range = self.loaded_module.example_range
        self.general_settings = getattr(self.loaded_module, 'general_settings', {})
```

#### Task 3.2: Update ALL Call Sites
```bash
# Find all places that call BuildModule methods
grep -r "build_module.run_model_check" src/
grep -r "build_module.compare_semantics" src/
grep -r "build_module.translate" src/

# Update each to use components directly:
# OLD: result = build_module.run_model_check(...)
# NEW: result = build_module.runner.run_model_check(...)
```

#### Task 3.3: Update run() Method
```python
    def run(self):
        """Execute the module based on flags."""
        if self.module_flags.comparison:
            self.comparison.run_comparison(
                self.loader.loaded_module,
                self.semantic_theories,
                self.module_flags.cpus
            )
        else:
            # Use runner for normal execution
            for example_name, example_case in self.example_range.items():
                for theory_name, theory in self.semantic_theories.items():
                    self.runner.process_example(
                        example_name, example_case, theory, 
                        self, self.module_flags
                    )
```

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

1. **Risk**: Breaking existing functionality
   - **Mitigation**: Update ALL call sites (no compatibility layer to miss)
   - **Mitigation**: Dual testing methodology catches issues

2. **Risk**: Circular dependencies between components
   - **Mitigation**: Components only reference BuildModule, not each other
   - **Mitigation**: Clear dependency direction enforced

3. **Risk**: Missing call sites during update
   - **Mitigation**: Systematic grep searches for all usages
   - **Mitigation**: Tests will fail if any missed

4. **Risk**: Performance regression
   - **Mitigation**: Profile before/after per IMPLEMENT.md
   - **Mitigation**: Fail-fast on performance degradation

## Implementation Order

1. **Create component files** (30 min)
   - Create empty modules with class structure
   - Add docstrings and method signatures

2. **Extract ModelRunner** (1 hour)
   - Move methods, fix imports
   - Update BuildModule integration
   - Test runner functionality

3. **Extract ModelComparison** (1 hour)
   - Move methods, handle multiprocessing
   - Update BuildModule integration
   - Test comparison functionality

4. **Extract OperatorTranslation** (30 min)
   - Move methods (simpler, no dependencies)
   - Update BuildModule integration
   - Test translation functionality

5. **Fix all tests** (1 hour)
   - Update imports and initialization
   - Fix any breaking changes
   - Verify coverage

6. **Manual testing** (30 min)
   - Run through protocol
   - Fix any issues found

7. **Cleanup and documentation** (30 min)
   - Remove old code
   - Update docs
   - Final verification

**Total Estimate**: 5 hours

## Appendix: Component Interaction Diagram

```
┌─────────────────┐
│   dev_cli.py    │
└────────┬────────┘
         │
┌────────▼────────┐
│   BuildModule   │ ← Pure coordinator (NO business logic)
├─────────────────┤
│ - module_flags  │
│ - components:   │
│   ├─ loader     │──────┐
│   ├─ runner     │──────┤
│   ├─ comparison │──────┤  Components reference parent
│   └─ translation│──────┤  for shared state ONLY
│ - run()         │      │
└─────────────────┘      │
         ▲               │
         └───────────────┘

Component responsibilities:
- loader: Module discovery and loading
- runner: Model checking execution  
- comparison: Multi-theory comparison
- translation: Operator conversion

NO delegation methods in BuildModule
ALL functionality in components
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
- [ ] DELETE all old methods from BuildModule
- [ ] NO delegation methods remain
- [ ] Update all documentation
- [ ] Verify clean architecture
- [ ] Performance verification

### Debugging Philosophy Checklist (per IMPLEMENT.md)
- [ ] Prefer deterministic failures
- [ ] Deep root cause analysis for any errors
- [ ] Implement systematic solutions
- [ ] Remove all cruft discovered

---

**Ready for Implementation**: This plan provides a systematic approach to completing the builder refactor with comprehensive testing at each step.