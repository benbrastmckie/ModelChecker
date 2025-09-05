# Implementation Plan: Builder Test Suite Refactoring

**Date**: 2025-09-05  
**Author**: AI Assistant  
**Status**: Not Started  
**Priority**: HIGH - Tests are critical for v1 stability  
**Related**: [002_builder_test_coverage.md](../findings/002_builder_test_coverage.md)  
**Focus**: Update builder test suite for new modular architecture

## Specification Validation

**Verification Checklist**:
- ✅ Clear phase breakdown (5 phases with specific tasks)
- ✅ Test requirements for each phase
- ✅ Success criteria (all tests passing, 100% coverage)
- ✅ Implementation tasks (detailed per phase)

## Executive Summary

Following the successful builder refactoring ([028](028_builder_v1_modular_refactor.md)), the test suite requires comprehensive updates to match the new modular architecture. Currently, 49 of 105 tests are failing due to:
- Tests expecting old delegation methods
- Missing tests for new modules (loader.py, serialize.py)
- Outdated method signatures and import structures

This plan addresses test maintenance, improves coverage from 80% to 100%, and ensures all tests pass.

## Current State Analysis

### Test Failure Categories

1. **API Changes** (31 failures)
   ```python
   # Old: module.run_model_check(...)
   # New: module.runner.run_model_check(...)
   ```

2. **Removed Methods** (11 failures)
   - `translate()` → `translation.translate()`
   - `compare_semantics()` → `comparison.compare_semantics()`
   - Delegation methods that no longer exist

3. **Import Structure** (7 failures)
   - Tests importing from wrong locations
   - Missing imports for new modules

### Coverage Gaps

| Module | Current Coverage | Target |
|--------|-----------------|--------|
| comparison.py | ✅ Tested | Enhance |
| example.py | ✅ Tested | Maintain |
| loader.py | ❌ **NOT TESTED** | Create tests |
| module.py | ✅ Tested | Update |
| project.py | ✅ Tested | Maintain |
| runner.py | ✅ Tested | Enhance |
| serialize.py | ❌ **NOT TESTED** | Create tests |
| translation.py | ✅ Tested | Update |
| validation.py | ✅ Tested | Maintain |
| z3_utils.py | ✅ Tested | Maintain |

## Implementation Plan

### Phase 1: Infrastructure Setup

**Objective**: Prepare test infrastructure for systematic updates

**Tasks**:
1. Create test mapping document
   ```python
   # Document old → new method mappings
   TEST_MIGRATIONS = {
       'module.run_model_check': 'module.runner.run_model_check',
       'module.translate': 'module.translation.translate',
       'module.compare_semantics': 'module.comparison.compare_semantics',
       # ... etc
   }
   ```

2. Set up test utilities
   ```python
   # test_helpers.py
   def create_test_module_with_components():
       """Create BuildModule with all components initialized."""
       module = BuildModule(flags)
       assert hasattr(module, 'runner')
       assert hasattr(module, 'translation')
       return module
   ```

**Success Criteria**:
- Test migration guide created
- Helper utilities implemented

### Phase 2: Fix Existing Test Failures

**Objective**: Update all failing tests to use new architecture

**Tasks by Test File**:

1. **test_baseline_simple.py**
   ```python
   # Update method existence checks
   def test_essential_components_exist(self):
       """Verify components exist on BuildModule."""
       module = BuildModule(mock_flags)
       self.assertTrue(hasattr(module, 'runner'))
       self.assertTrue(hasattr(module.runner, 'run_model_check'))
   ```

2. **test_module.py**
   ```python
   # Update method calls
   def test_run_model_check_logos(self):
       # Old: result = build_module.run_model_check(...)
       # New:
       result = build_module.runner.run_model_check(...)
   ```

3. **test_comparison_extraction.py**
   ```python
   # Update delegation tests
   def test_build_module_uses_comparison(self):
       # Test direct component usage
       module.comparison.compare_semantics(...)
   ```

**Success Criteria**:
- All 49 failing tests updated and passing
- No regression in passing tests

### Phase 3: Create Missing Unit Tests

**Objective**: Achieve 100% module coverage

#### 3.1 Create test_loader.py

```python
"""Unit tests for ModuleLoader."""

class TestModuleLoader(unittest.TestCase):
    def test_load_module_success(self):
        """Test successful module loading."""
        
    def test_load_module_file_not_found(self):
        """Test handling of missing files."""
        
    def test_project_detection(self):
        """Test is_generated_project logic."""
        
    def test_find_project_directory(self):
        """Test project root discovery."""
        
    def test_load_attribute_validation(self):
        """Test attribute loading and validation."""
        
    def test_sys_path_management(self):
        """Test proper sys.path handling."""
```

#### 3.2 Create test_serialize.py

```python
"""Unit tests for serialization utilities."""

class TestSerialization(unittest.TestCase):
    def test_serialize_semantic_theory(self):
        """Test theory serialization."""
        
    def test_deserialize_semantic_theory(self):
        """Test theory deserialization."""
        
    def test_round_trip_preservation(self):
        """Test data integrity through serialization."""
        
    def test_complex_object_handling(self):
        """Test handling of Z3 objects, classes, etc."""
        
    def test_error_cases(self):
        """Test handling of non-serializable objects."""
```

**Success Criteria**:
- 100% coverage for loader.py
- 100% coverage for serialize.py
- All edge cases tested

### Phase 4: Integration Testing

**Objective**: Verify component interactions work correctly

**New Integration Tests**:

1. **test_component_integration.py**
   ```python
   def test_runner_translation_integration(self):
       """Test runner uses translation correctly."""
       
   def test_comparison_serialization_integration(self):
       """Test comparison uses serialization for multiprocessing."""
       
   def test_full_workflow_integration(self):
       """Test complete example execution flow."""
   ```

2. **test_error_propagation.py**
   ```python
   def test_loader_error_handling(self):
       """Test error propagation from loader."""
       
   def test_component_initialization_failures(self):
       """Test handling of component creation errors."""
   ```

**Success Criteria**:
- Component interactions verified
- Error paths tested
- No integration gaps

### Phase 5: Documentation and Cleanup

**Objective**: Ensure test suite is maintainable

**Tasks**:
1. Update test documentation
   ```python
   """
   Test Organization:
   - Unit tests: One file per module
   - Integration tests: test_component_integration.py
   - Workflow tests: test_integration_workflow.py
   """
   ```

2. Remove obsolete tests
   - Tests for removed delegation methods
   - Tests for old static methods
   - Duplicate test cases

3. Add coverage reporting
   ```bash
   # Add to run_tests.py
   pytest --cov=model_checker.builder --cov-report=html
   ```

**Success Criteria**:
- Clear test organization
- No obsolete tests
- Coverage reports available

## Testing Strategy

### Test Levels

1. **Unit Tests** (per module)
   - Direct function/method testing
   - Mock dependencies
   - Edge case coverage

2. **Integration Tests** (component interactions)
   - Real component instances
   - Minimal mocking
   - Workflow verification

3. **System Tests** (end-to-end)
   - Full example execution
   - Real file I/O
   - Performance validation

### Coverage Goals

| Level | Current | Target |
|-------|---------|--------|
| Module Coverage | 80% | 100% |
| Line Coverage | ~60% | >90% |
| Branch Coverage | Unknown | >80% |

## Success Metrics

1. **Immediate Success**
   - All 105 tests passing
   - 100% module coverage
   - No test warnings

2. **Quality Metrics**
   - Tests run in <30 seconds
   - Clear test output
   - Maintainable test code

3. **Long-term Success**
   - Easy to add new tests
   - Tests catch real bugs
   - Tests document behavior

## Risk Mitigation

### Risks
1. **Breaking changes during test updates**
   - Mitigation: Run tests frequently
   - Backup: Git commits after each phase

2. **Missing edge cases**
   - Mitigation: Code coverage analysis
   - Backup: Fuzzing/property tests

3. **Test maintenance burden**
   - Mitigation: Clear organization
   - Backup: Test generation tools

## Implementation Order

1. Phase 1: Infrastructure (2 hours)
2. Phase 2: Fix failures (4 hours)
3. Phase 3: Missing tests (3 hours)
4. Phase 4: Integration (2 hours)
5. Phase 5: Documentation (1 hour)

**Total Estimate**: 12 hours

## Appendix: Test Migration Examples

### Example 1: Method Call Updates
```python
# OLD
def test_translate(self):
    result = module.translate(case, dict)
    
# NEW
def test_translate(self):
    result = module.translation.translate(case, dict)
```

### Example 2: Component Testing
```python
# OLD
@patch('model_checker.builder.module.BuildModule.run_comparison')
def test_comparison(self, mock_method):
    ...
    
# NEW
def test_comparison(self):
    module = BuildModule(flags)
    result = module.comparison.run_comparison()
```

### Example 3: Import Updates
```python
# OLD
from model_checker.builder import BuildModule

# NEW
from model_checker.builder import BuildModule
from model_checker.builder.runner import ModelRunner
from model_checker.builder.loader import ModuleLoader
```

---

**Next Steps**: Begin with Phase 1 infrastructure setup, then systematically update tests following the new architecture patterns.