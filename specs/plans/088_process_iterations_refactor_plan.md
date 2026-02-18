# Plan 088: Process Iterations Method Refactoring

**Status:** For Review
**Priority:** P1 (Critical)
**Complexity:** High
**Risk Level:** High - Core iteration logic affects multiple theories
**Target Module:** src/model_checker/builder/runner.py::process_iterations

## Executive Summary

The `process_iterations` method (157 lines) is a complex method handling model iteration logic across different theory implementations. This plan proposes a careful, incremental refactoring to improve maintainability while preserving all functionality.

## Current State Analysis

### Method Overview

- **Location:** runner.py lines 521-677
- **Line Count:** 157 lines (exceeds 75-line limit by 82 lines)
- **Complexity:** High - multiple nested conditions, error handling, theory discovery
- **Dependencies:** Heavily coupled with theory_lib iteration implementations

### Functional Responsibilities

1. **Theory Discovery** (lines 543-564)
   - Dynamically discover theory module for iteration
   - Import theory module and locate iterate function
   - Handle both generator and list-based interfaces

2. **Interface Detection** (lines 566-572)
   - Check for generator vs list interface
   - Route to appropriate iteration handler

3. **List-Based Iteration** (lines 573-676)
   - Process model structures list
   - Skip isomorphic models
   - Calculate and display differences
   - Handle model numbering and display
   - Capture and save output for each model

4. **Error Handling** (lines 673-676)
   - Catch and report iteration errors
   - Provide stack traces for debugging

### Key Challenges

1. **Theory-Specific Logic:** Different theories have different iteration interfaces
2. **State Management:** Tracks previous models, differences, numbering
3. **Display Logic:** Complex formatting for model differences and headers
4. **Legacy Support:** Maintains compatibility with multiple interface versions

## Proposed Refactoring Strategy

### Phase 1: Extract Theory Discovery (20 lines → separate method)

```python
def _discover_iteration_function(
    self,
    theory_name: TheoryName,
    semantic_theory: TheoryDict
) -> Callable:
    """Discover and load the theory-specific iteration function."""
```

### Phase 2: Extract Model Difference Calculation (25 lines → separate method)

```python
def _calculate_model_differences(
    self,
    current_structure: Any,
    previous_structure: Any,
    index: int,
    model_structures: List[Any]
) -> None:
    """Calculate differences between current and previous model."""
```

### Phase 3: Extract Model Display Logic (30 lines → separate method)

```python
def _display_iteration_model(
    self,
    example: 'BuildExample',
    structure: Any,
    example_name: str,
    theory_name: TheoryName,
    distinct_count: int,
    expected_total: int,
    is_first: bool
) -> None:
    """Display a single iteration model with appropriate formatting."""
```

### Phase 4: Extract Summary and Debug Output (15 lines → separate method)

```python
def _display_iteration_summary(
    self,
    example: 'BuildExample',
    model_structures: List[Any]
) -> None:
    """Display iteration summary and debug messages."""
```

### Phase 5: Simplify Main Method (< 75 lines)

The main `process_iterations` method will orchestrate the extracted methods:

```python
def process_iterations(self, ...) -> None:
    """Process iterations for an example that supports model iteration."""
    try:
        # Discover iteration function (5 lines)
        theory_iterate_example = self._discover_iteration_function(
            theory_name, semantic_theory
        )

        # Check interface type and route (10 lines)
        if self._is_generator_interface(theory_iterate_example):
            self._run_generator_iteration(...)
            return

        # Run list-based iteration (50 lines)
        self._run_list_iteration(
            example, theory_iterate_example,
            example_name, theory_name, iterate_count
        )

    except Exception as e:
        self._handle_iteration_error(e)
```

## Implementation Steps

### Step 1: Create Helper Methods

1. Add `_discover_iteration_function` method
2. Add `_is_generator_interface` method
3. Add `_calculate_model_differences` method
4. Add `_display_iteration_model` method
5. Add `_display_iteration_summary` method
6. Add `_handle_iteration_error` method

### Step 2: Create Main Orchestration Method

1. Add `_run_list_iteration` method (consolidates list-based logic)
2. Update `process_iterations` to use new methods

### Step 3: Test Each Extraction

1. Run builder tests after each method extraction
2. Test with actual iteration examples
3. Verify output formatting remains identical

## Risk Mitigation

### Testing Strategy

1. **Unit Tests:** Test each extracted method independently
2. **Integration Tests:** Verify iteration workflow
3. **Theory Tests:** Test with each theory that supports iteration
4. **Output Comparison:** Compare output before/after refactoring

### Rollback Plan

1. Keep original method commented during development
2. Use git commits after each successful extraction
3. Test thoroughly before removing original

### Critical Areas to Preserve

1. **Model Numbering:** Must maintain exact numbering scheme
2. **Difference Detection:** Must preserve all difference calculations
3. **Display Format:** Output must remain identical
4. **Error Messages:** Must preserve all error reporting

## Success Metrics

### Required Outcomes

- Method under 75 lines
- All 218 builder tests passing
- Identical output for iteration examples
- No performance degradation
- Improved code clarity

### Validation Commands

```bash
# Run builder tests
pytest src/model_checker/builder/tests/ -v

# Test iteration with logos theory
./dev_cli.py -i 5 src/model_checker/theory_lib/logos/subtheories/counterfactual/examples.py

# Test iteration with exclusion theory
./dev_cli.py -i 3 src/model_checker/theory_lib/exclusion/examples.py

# Test iteration with imposition theory
./dev_cli.py -i 4 src/model_checker/theory_lib/imposition/examples.py
```

## Code Structure After Refactoring

```python
class ModelRunner:
    # Main orchestration (< 75 lines)
    def process_iterations(self, ...) -> None

    # Theory discovery (20 lines)
    def _discover_iteration_function(self, ...) -> Callable

    # Interface checking (10 lines)
    def _is_generator_interface(self, ...) -> bool

    # List iteration handler (60 lines)
    def _run_list_iteration(self, ...) -> None

    # Model difference calculation (25 lines)
    def _calculate_model_differences(self, ...) -> None

    # Model display (30 lines)
    def _display_iteration_model(self, ...) -> None

    # Summary display (15 lines)
    def _display_iteration_summary(self, ...) -> None

    # Error handling (10 lines)
    def _handle_iteration_error(self, ...) -> None
```

## Notes and Warnings

### Critical Dependencies

- Theory modules must provide `iterate_example` or `iterate_example_generator`
- Model structures must support difference detection methods
- Output manager must handle iteration numbering

### Backward Compatibility

- Must support both generator and list interfaces
- Must handle legacy `calculate_model_differences` method
- Must preserve isomorphism detection behavior

### Performance Considerations

- Method extraction should not impact iteration performance
- Avoid unnecessary object creation in loops
- Maintain efficient difference calculation

## Review Checklist

- [ ] Theory discovery logic preserved
- [ ] Interface detection accurate
- [ ] Model numbering correct
- [ ] Difference calculation intact
- [ ] Display formatting unchanged
- [ ] Error handling comprehensive
- [ ] All tests passing
- [ ] Output identical to original

---

**Next Steps:** Review this plan, then proceed with careful implementation following the outlined steps. Test thoroughly after each extraction to ensure no functionality is lost.
