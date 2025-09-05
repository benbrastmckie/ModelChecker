# Implementation Plan: Builder Test Suite Cleanup and Manual Testing Protocol

**Date**: 2025-09-05  
**Author**: AI Assistant  
**Status**: Partially Implemented - Runtime error fixed, manual testing documented  
**Priority**: HIGH - Tests pass but manual testing reveals runtime errors  
**Related**: [029_builder_test_refactor.md](029_builder_test_refactor.md), [TESTING_STANDARDS.md](../../../maintenance/TESTING_STANDARDS.md)  
**Focus**: Clean up builder test suite and fix manual testing failures

## Specification Validation

**Verification Checklist**:
- ✅ Clear problem statement (manual tests failing despite passing unit tests)
- ✅ Cruft identification (3 files to remove)
- ✅ Test reorganization plan
- ✅ Manual testing protocol establishment
- ✅ Fix for discovered runtime errors

## Executive Summary

While all builder unit tests pass, manual testing with `dev_cli.py` reveals runtime errors that were not caught by the test suite. This indicates:

1. **Test coverage gaps** - Tests don't exercise the actual runtime paths
2. **Method signature conflicts** - `discover_theory_module` has duplicate definitions
3. **Need for manual testing protocol** - Automated tests alone are insufficient

This plan addresses test suite cleanup, establishes manual testing protocols, and fixes the discovered runtime errors.

## Current State Analysis

### Discovered Issues

1. **Runtime Error in dev_cli.py**:
   ```
   Error during iteration: ModuleLoader.discover_theory_module() takes 1 positional argument but 3 were given
   ```
   - Two methods with same name but different signatures in `loader.py`
   - Lines 28-85: `discover_theory_module(self, theory_name, semantic_theory)`
   - Lines 149-165: `discover_theory_module(self)`

2. **Test Suite Cruft**:
   - `migrate_tests.py` - One-time migration script
   - `test_refactor_baseline.py` - Temporary refactor validation
   - `baseline/` directory - Unused output captures

3. **Test Organization Issues**:
   - Large test files (test_module.py: 463 lines)
   - Duplicate test patterns
   - No manual testing protocol documented

## Root Cause Analysis

The tests pass because:
1. They mock the loader behavior rather than testing actual integration
2. The duplicate method issue only surfaces during iteration (not initial load)
3. No integration tests run the full dev_cli.py workflow

## Implementation Plan

### Phase 1: Fix Runtime Errors (URGENT)

**Objective**: Fix the immediate runtime error blocking manual testing

#### Task 1.1: Rename Duplicate Method
```python
# In loader.py, rename the 3-argument version (line 28):
def discover_theory_module_for_iteration(self, theory_name, semantic_theory):
    """Dynamically discover which theory module a semantic theory belongs to.
    
    Used during iteration to find the correct theory module.
    """
    # ... existing implementation ...

# Update runner.py (line 373) to use new name:
module_name = self.build_module.loader.discover_theory_module_for_iteration(theory_name, semantic_theory)
```

#### Task 1.2: Add Integration Test
```python
# test_dev_cli_integration.py
def test_theory_library_examples_execution():
    """Test that dev_cli.py can run theory library examples."""
    examples = [
        "src/model_checker/theory_lib/logos/examples.py",
        "src/model_checker/theory_lib/logos/subtheories/modal/examples.py",
        "src/model_checker/theory_lib/exclusion/examples.py",
    ]
    
    for example_path in examples:
        # Actually run the example through the full pipeline
        # Not just mock it
        result = subprocess.run([
            sys.executable, "dev_cli.py", example_path
        ], capture_output=True, text=True)
        
        assert result.returncode == 0, f"Failed to run {example_path}: {result.stderr}"
```

### Phase 2: Update Testing Standards

**Objective**: Document manual testing requirements in maintenance docs

#### Task 2.1: Create MANUAL_TESTING.md
```markdown
# Manual Testing Protocol

## Why Manual Testing is Required

Unit tests alone cannot catch all integration issues because:
1. Mocking can hide interface mismatches
2. Full pipeline execution reveals runtime errors
3. Theory library integration requires proper import handling

## Manual Test Checklist

### Before Each Release
Run these manual tests to verify functionality:

#### 1. Theory Library Examples
```bash
# Test each theory's main examples
./dev_cli.py src/model_checker/theory_lib/logos/examples.py
./dev_cli.py src/model_checker/theory_lib/exclusion/examples.py
./dev_cli.py src/model_checker/theory_lib/imposition/examples.py
./dev_cli.py src/model_checker/theory_lib/bimodal/examples.py

# Test subtheory examples
./dev_cli.py src/model_checker/theory_lib/logos/subtheories/modal/examples.py
./dev_cli.py src/model_checker/theory_lib/logos/subtheories/counterfactual/examples.py
./dev_cli.py src/model_checker/theory_lib/logos/subtheories/constitutive/examples.py
./dev_cli.py src/model_checker/theory_lib/logos/subtheories/relevance/examples.py
./dev_cli.py src/model_checker/theory_lib/logos/subtheories/extensional/examples.py
```

#### 2. Generated Projects
```bash
# Generate and test a project
./model-checker  # Choose logos, create project
./dev_cli.py project_*/examples.py
```

#### 3. Iteration Testing
```bash
# Test iteration with various theories
./dev_cli.py -i src/model_checker/theory_lib/logos/examples.py
# When prompted, enter 5 to test multiple iterations
```

### Expected Behavior
- No Python errors or tracebacks
- Examples execute and show model output
- Iteration prompts work correctly
```

#### Task 2.2: Update TESTING_STANDARDS.md
Add new section after line 235:

```markdown
### Manual Testing Requirements

In addition to automated tests, manual testing is REQUIRED because:

1. **Integration Coverage**: Unit tests with mocks cannot catch all integration issues
2. **Import Resolution**: Theory library imports behave differently in real execution
3. **Runtime Errors**: Method signature mismatches only appear during actual use

See [MANUAL_TESTING.md](MANUAL_TESTING.md) for the complete manual testing protocol.

**Critical**: All manual tests must pass before marking any PR as ready for merge.
```

### Phase 3: Test Suite Cleanup

**Objective**: Remove cruft and reorganize tests

#### Task 3.1: Remove Cruft Files
```bash
# Execute cleanup
rm migrate_tests.py
rm test_refactor_baseline.py
rm -rf baseline/

# Update README.md to remove references
```

#### Task 3.2: Implement conftest.py
Already created - standardizes fixtures across all tests

#### Task 3.3: Consolidate Related Tests
```python
# Merge extraction tests into test_components.py
class TestComponentExtraction:
    """Test all extracted components."""
    
    def test_runner_extraction(self):
        # From test_runner_extraction.py
        
    def test_comparison_extraction(self):
        # From test_comparison_extraction.py
        
    def test_translation_extraction(self):
        # From test_translation_extraction.py
```

### Phase 4: Add Missing Integration Tests

**Objective**: Ensure test coverage catches runtime errors

#### Task 4.1: Create test_full_pipeline.py
```python
"""Full pipeline integration tests that catch runtime errors."""

class TestFullPipeline:
    """Test complete execution paths without mocking."""
    
    def test_theory_library_execution(self):
        """Test running theory library examples end-to-end."""
        # No mocks - actual execution
        
    def test_iteration_workflow(self):
        """Test iteration with discover_theory_module calls."""
        # Verifies the method signature issue would be caught
        
    def test_generated_project_workflow(self):
        """Test full project generation and execution."""
        # Catches import issues
```

## Success Metrics

1. **Manual Tests Pass**: All commands in manual testing protocol execute without errors
2. **Runtime Error Fixed**: `discover_theory_module` error resolved
3. **Test Coverage**: Integration tests catch the issues that unit tests missed
4. **Cleanup Complete**: Cruft removed, tests reorganized

## Testing Strategy

### Two-Pronged Approach
1. **Automated Tests** (`./run_tests.py --package builder`):
   - Unit test coverage
   - Fast feedback during development
   - CI/CD integration

2. **Manual Tests** (see MANUAL_TESTING.md):
   - Integration verification
   - Runtime error detection
   - Release validation

### Why Both Are Necessary
- Mocked unit tests verify component behavior in isolation
- Manual tests verify the components work together in practice
- Runtime errors often only appear in full integration

## Implementation Order

1. **URGENT - Fix Runtime Error** (Phase 1):
   - Rename duplicate method
   - Update caller
   - Add regression test

2. **Document Manual Testing** (Phase 2):
   - Create MANUAL_TESTING.md
   - Update TESTING_STANDARDS.md
   - Add to PR checklist

3. **Clean Up Tests** (Phase 3):
   - Remove cruft
   - Consolidate files
   - Update documentation

4. **Add Integration Tests** (Phase 4):
   - Create full pipeline tests
   - Ensure future issues are caught

## Risk Mitigation

- **Risk**: Breaking changes during cleanup
  - **Mitigation**: Run full test suite after each change
  
- **Risk**: Missing other runtime errors
  - **Mitigation**: Comprehensive manual test protocol
  
- **Risk**: Future regressions
  - **Mitigation**: Integration tests that exercise full pipeline

## Remaining Tasks from Previous Spec

From [029_builder_test_refactor.md](029_builder_test_refactor.md), the following remain incomplete:

### Test Documentation (from Phase 0)
- Create comprehensive `/src/model_checker/builder/tests/README.md` with complete file tree
- Document test categories, coverage metrics, and execution instructions
- This aligns with TESTING_STANDARDS.md requirements

### Test Utilities and Fixtures (from Phase 1)
- Create `/src/model_checker/builder/tests/fixtures.py` with shared test data
- Add test helpers with descriptive assertions
- Standardize mock objects and test configurations

### Coverage Enhancement (from Phase 3)
- Enhance test_loader.py with edge cases and parameterized tests
- Add test_serialize.py coverage for round-trip preservation
- Achieve 100% module coverage goals

### Integration Testing (from Phase 4)
- Create test_component_integration.py for interaction testing
- Add test_error_propagation.py for error path verification
- Ensure no integration gaps remain

## Appendix: Complete File List

### Files to Remove
- `/src/model_checker/builder/tests/migrate_tests.py`
- `/src/model_checker/builder/tests/test_refactor_baseline.py`
- `/src/model_checker/builder/tests/baseline/`

### Files to Create
- `/Code/maintenance/MANUAL_TESTING.md` ✅ (COMPLETED)
- `/src/model_checker/builder/tests/test_full_pipeline.py` ✅ (COMPLETED)
- `/src/model_checker/builder/tests/test_components.py` (consolidated)
- `/src/model_checker/builder/tests/README.md` (comprehensive documentation)
- `/src/model_checker/builder/tests/fixtures.py` (shared test data)
- `/src/model_checker/builder/tests/test_component_integration.py` (interaction tests)
- `/src/model_checker/builder/tests/test_error_propagation.py` (error path tests)

### Files to Update
- `/src/model_checker/builder/loader.py` ✅ (rename method - COMPLETED)
- `/src/model_checker/builder/runner.py` ✅ (update method call - COMPLETED)
- `/Code/maintenance/TESTING_STANDARDS.md` ✅ (add manual testing - COMPLETED)
- `/src/model_checker/builder/tests/README.md` (remove cruft references, add comprehensive docs)
- `/src/model_checker/builder/tests/test_loader.py` (enhance with edge cases)
- `/src/model_checker/builder/tests/test_serialize.py` (add parameterized tests)